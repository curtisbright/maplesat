<?php
ob_start('ob_gzhandler');
error_reporting(E_ALL | E_STRICT);
ini_set('display_errors',1);

$username="cmsat_presenter";

#this is for my local MySQL install, not my website
#sorry for getting your hopes up
$password="neud21kahgsdk";
$database="cmsat";

$sql = new mysqli("localhost", $username, $password, $database);
if (mysqli_connect_errno()) {
    printf("Connect failed: %s\n", mysqli_connect_error());
    die();
}
//print_r($sql);
?>
